-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = (box.Text:gsub("%s+", "")) -- trim spaces; keep case (work.ink tokens are lowercase)
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'CnVd4BnKMEQfvPFtYvidoD2L'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-G4nbOhozPrBu
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, watermark = 'Y2k-G4nbOhozPrBu', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
