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
			local key = box.Text:upper()
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

local __k = 'dMr7RNNwfP4C4wmqKPC8o6ii'
local __p = 'SWBS1cferOL2sqHT1uL9k97Aoa3/1Pz5htji1cferOL2sqHT1uL9k97Aoa3/1Pz5htji1cferOL2sqHT1uL9k97Aoa3/1Pz5htji1cferOL2sqHT1uL9k97Aoa3/1Pz5htji1cferOL2sqHT1uL9k97Aoa3/1Pz5htji1cferOL2sqHT1uL9k97Aoa3/1Pz5htji1cferOL2sqHT1uL9k97Aoa3/1Pz5htji1cferOL2sqHT1uL9k97Aoa3/1Pz5htji1cferOL2WhluFFc+FCc8Y1lPegwECyNSfycsbgtGJgVtBH1AXGtwFnFPDEkmBj4bUzsvICIvcBwaBhxNIigiKkgbFisIByZAdTMtJV5sfRljFDAMHC5weRg8UwUFRCxSezcjIRlGfxQVURkJAy5wJ10cFgoAED8dWSFuMlc2PFUgUT4JUXxpcQ5XBVBaVHpAA2Z6RFpLcNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44UFaKl5PWAYdRCoTWjd0BwQqP1UnURNFWGskK10BFg4ICShcez0vKhICamMiXQNFWGs1LVxlPERERK/mu7DazpXy0NbXtJX58anEw9r7tov95K/mt7DazpXy0NbXtJX58anEw9r7tov95K/mt7DazpXy0NbXtJX58anEw9r7tov95K/mt7DazpXy0NbXtJX58anEw9r7tov95K/mt7DazpXy0NbXtJX58anEw9r7tov95K/mt7DazpXy0NbXtJX58anEw9r7tov95K/mt7DazpXy0NbXtJX58anEw9r7tov95K/mt7DazpXy0NbXtJX58anEw9r7tov99EdfGnKs2vVGcHsBZz4pOAoeY20mFklJRG1SF3JubldGcBRjFFdNUWtwYxhPFklJRG1SF3JubldGcBRjFFdNUWtwYxhPFkmL8M94Gn9urOPysqDD1uPtk9/Qoazv1P3phtny1cbOrOPmsqDD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QRkJUGl5SRhPFklJRG1SUjwqRFdGcBQmWhNBezZ5STIiWR8MNnczUzYMOwMSP1prT31NUWtwF10XQlRLMB1SQz1uAx4IOVMiWRIeU2daYxhPFi8cCi5PUScgLQMPP1prHX1NUWtwYxhPFgUGByweFzEmLwVGbRQPWxQMHRs8IkEKREcqDCwAVjE6KwVscBRjFFdNUWs8LFsOWkkbCyIGF29uLR8HIhQiWhNNEiMxMQIpXwcNIiQARCYNJh4KNBxhfAIAECU/Klw9WQYdNCwAQ3BnRFdGcBRjFFdNGC1wMVcAQkkdDCgcPXJubldGcBRjFFdNUS0/MRgwGkkGBidSXjxuJwcHOUYwHCACAyAjM1kMU1MuATk2UiEtKxkCMVo3R19EWGs0LDJPFklJRG1SF3JubldGcBRjXRFNHik6bXYOWwxJWXBSFR8nIB4BMVkmFCUMEi5yY1kBUkkGBidIfiEPZlUrP1AmWFVEUT84JlZlFklJRG1SF3JubldGcBRjFFdNUWsiLFcbGCovFiwfUnJzbhgEOg4EUQM9GD0/NxBGFkJJMigRQz08fVkINUNrBFtNRGdwcxFlFklJRG1SF3JubldGcBRjFFdNUWscKlodVxsQXgMdQzsoN19EBFEvUQcCAz81JxgbWUkkDSMbUDMjKwRHch1JFFdNUWtwYxhPFklJRG1SF3JublcUNUA2RhlnUWtwYxhPFklJRG1SF3JubhIIND5jFFdNUWtwYxhPFkkMCil4F3JubldGcBRjFFdNPSIyMVkdT1MnCzkbUStmbDoPPl0kVRoIAms+LExPUAYcCilTFXtEbldGcBRjFFcIHy9aYxhPFgwHAGF4SntERFpLcNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov89K/np7Db3pXzwNbWpJX44UF9bhhPcTsoNAU7dAFuGjYkWhluFJX44anF09r6pov89K/np7Db3pXzwNbWpJX44anF09r6pov8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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-SAXcLvTYqxYe
return Vm.run(__src, { name = 'Sell a Lemon/Sell a Lemon', checksum = 2454316622, interval = 2, watermark = 'Y2k-SAXcLvTYqxYe', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
