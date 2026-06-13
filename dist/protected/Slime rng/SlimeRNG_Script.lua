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

local __k = 'mLQMQ1rtv6BwCcv2vKPlPo9i'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-UsU4GM4mvIBB
return Vm.run(__src, { name = 'Slime rng/SlimeRNG_Script', checksum = 156284418, interval = 2, watermark = 'Y2k-UsU4GM4mvIBB', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
